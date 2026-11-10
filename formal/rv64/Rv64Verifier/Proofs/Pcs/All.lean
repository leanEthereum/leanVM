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
import Rv64Verifier.Proofs.Pcs.VsoFinalTail
import Rv64Verifier.Proofs.Pcs.VsoKernel
import Rv64Verifier.Proofs.Pcs.VsoOpenOA
import Rv64Verifier.Proofs.Pcs.VsoKernelCall
import Rv64Verifier.Proofs.Pcs.VsoUniform
import Rv64Verifier.Proofs.Pcs.VsoFinalToCheck
import Rv64Verifier.Proofs.Pcs.VsoGlueLoop
import Rv64Verifier.Proofs.Pcs.VsoGlueRoots
import Rv64Verifier.Proofs.Pcs.VsoGlueInvs
import Rv64Verifier.Proofs.Pcs.VsoGlueProds
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Pcs.VsoTailLevel
import Rv64Verifier.Proofs.Pcs.VsoLeaves
import Rv64Verifier.Proofs.Hash.All

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

/-- `extend_desugared`'s contract as `walk`'s R21 calls it. -/
theorem extendE : Walk.ExtendSpecE :=
  Extend.extend_spec Multilinear.selectorPoint Multilinear.sliceConcat Runtime.growAmortized

theorem extend : ExtendSpec := by
  intro s hpc hpre
  obtain ⟨t, hr, h⟩ := extendE s hpc { hpre with points := fun i hi ↦ Or.inr (hpre.points i hi) }
  exact ⟨t, hr, h.imp_left fun ⟨hpc', hpres, hpost⟩ ↦ ⟨hpc', hpres, hpost.toExtendPost⟩⟩

/-- `verify_stacked_opening`'s contract, its callees in the final level's terminal check proved,
from the level loop and the tail up to that check. -/
theorem vsoSpec (hL : Vso.LoopSpec Transcript.OpeningsAt) (hT : Vso.ToCheck Transcript.OpeningsAt) :
    VsoSpec Transcript.OpeningsAt :=
  Vso.vsoSpec_of Multilinear.mleEval Field.mul hL hT

/-- The final level's tail up to the terminal check, its callees proved, from the glued claims'
loop. -/
theorem toCheck (hGl : Vso.GluedSpec Transcript.OpeningsAt) : Vso.ToCheck Transcript.OpeningsAt :=
  Vso.toCheck_of Transcript.duplex Transcript.polyEval Runtime.growOneFresh_80011c78 roundPolyErr
    Multilinear.sliceConcat basis hGl

/-- The glued claims' loop, its callees and `induced_weight`'s pieces proved. -/
theorem gluedClosed : Vso.GluedSpec Transcript.OpeningsAt :=
  Vso.gluedSpec EqEval.eq_eval_proved
    (Vso.roots_spec Runtime.alloc_spec tryAllocZeroed Runtime.reserveFast_8000d628 Field.kSquare
      Field.baseMul Runtime.memmove Runtime.growOneFresh_8000d7bc)
    (Vso.invs_spec tryAllocZeroed Runtime.reserveFast_8000d628 Field.kInv)
    (Vso.prods_spec Field.baseMul Field.mulK Field.mul Field.kSquare) Field.mul

/-- **The final level's tail up to the terminal check**, with no hypothesis. -/
theorem toCheckClosed : Vso.ToCheck Transcript.OpeningsAt := toCheck gluedClosed

/-- The callees of a level of `verify_stacked_opening`'s loop. -/
theorem levelCallees : Vso.LevelCallees :=
  ⟨Transcript.duplex, Runtime.growOneFresh_80011c78, Transcript.polyEval, roundPolyErr,
    Transcript.nextScalars, Transcript.samples, Transcript.nextScalar,
    Runtime.growOneFresh_8000c7d0, Transcript.absorb, tryAllocZeroed, Multilinear.powers,
    Runtime.reserveFast_8000c898, Runtime.memcpy, Hash.keccakHash, Runtime.Memcmp.memcmp_spec,
    Multilinear.eqKernel⟩

/-- The glue of a level's pending claims. -/
theorem glue : Vso.GlueSpec :=
  Vso.glueSpec Field.mul Runtime.memcpy Runtime.growOneFresh_8000db78

/-- A level's tail, from the rows' values. -/
theorem levelTail : Vso.LevelTail :=
  Vso.levelTail Multilinear.dot roundPolyErr Runtime.growOneFresh_8000c7d0 glue

/-- **`verify_stacked_opening`'s level loop**, from the two paths of a level's rows. -/
theorem loopSpec (h0 : Vso.RowsZero) (hD : Vso.RowsDeep) : Vso.LoopSpec Transcript.OpeningsAt :=
  Vso.loopSpec_of levelCallees Multilinear.dot Runtime.alloc_spec Runtime.growOneFresh_8000d7bc h0 hD
    Vso.leavesSpec levelTail

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

/-- info: 'Rv64Verifier.Proofs.Pcs.extendE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.extendE

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

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.exitR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.exitR

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.vso_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.vso_of

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.check

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.afterGlue_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.afterGlue_final

/-- info: 'Rv64Verifier.Proofs.Pcs.vsoSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.vsoSpec
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.RunsK.merkle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.RunsK.merkle
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.stackShape_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.stackShape_eq
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.mr_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.mr_lt
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.qbuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.qbuf
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.levelMerkle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.levelMerkle
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.levelFoldedMerkle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.levelFoldedMerkle
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.copyLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.copyLoop
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.slices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.slices
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.Merkled.toSlices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.Merkled.toSlices
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.openingAt_of_pathAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.openingAt_of_pathAt
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.vsoOpeningsAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.vsoOpeningsAt_of
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.vsoOpenMem_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.vsoOpenMem_of
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.abfcA_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.abfcA_bytes
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.digestBits_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.digestBits_bytes
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.DFrame.bytesU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.DFrame.bytesU
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.callEqKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.callEqKernel
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.kernel
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.Kerneled.lvl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.Kerneled.lvl
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.rowsBranch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.rowsBranch
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.Merkled.keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.Merkled.keep
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.Slices.keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.Slices.keep

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.tRounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.tRounds

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.tPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.tPoint

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.claims_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.claims_keep

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.tBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.tBasis

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.tEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.tEmpty

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.afterTail_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.afterTail_basis

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.toCheck_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.toCheck_of

/-- info: 'Rv64Verifier.Proofs.Pcs.toCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.toCheck

/-- info: 'Rv64Verifier.Proofs.Pcs.gluedClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.gluedClosed

/-- info: 'Rv64Verifier.Proofs.Pcs.toCheckClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.toCheckClosed

/-- info: 'Rv64Verifier.Proofs.Pcs.glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.glue

/-- info: 'Rv64Verifier.Proofs.Pcs.levelTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.levelTail

/-- info: 'Rv64Verifier.Proofs.Pcs.loopSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.loopSpec

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.tailFront' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.tailFront

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.glueIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.glueIn

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.nextHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.nextHead

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.finalIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.finalIn

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.backEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.backEdge

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.atR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.atR

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.leavesSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.leavesSpec

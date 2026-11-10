import Rv64Verifier.Proofs.Walk.R17B
import Rv64Verifier.Proofs.Walk.R17C
import Rv64Verifier.Proofs.Walk.ErrTail
import Rv64Verifier.Proofs.Walk.TailModel
import Rv64Verifier.Proofs.Walk.Keeps
import Rv64Verifier.Proofs.Walk.Spec
import Rv64Verifier.Proofs.Walk.R17E
import Rv64Verifier.Proofs.Walk.R18C
import Rv64Verifier.Proofs.Walk.TailStages
import Rv64Verifier.Proofs.Walk.R18K
import Rv64Verifier.Proofs.Walk.TailG
import Rv64Verifier.Proofs.Walk.R19A
import Rv64Verifier.Proofs.Walk.R22C
import Rv64Verifier.Proofs.Walk.R19M
import Rv64Verifier.Proofs.Walk.R20I
import Rv64Verifier.Proofs.Walk.R19N

/-!
# `walk` from `AtR17`: the regions proved so far, and the assembly of its contract

The axioms: Lean's three.
-/

/-- info: 'Rv64Verifier.Proofs.Walk.r17a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r17a

/-- info: 'Rv64Verifier.Proofs.Walk.r17b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r17b

/-- info: 'Rv64Verifier.Proofs.Walk.duplexW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.duplexW

/-- info: 'Rv64Verifier.Proofs.Walk.sample_lanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.sample_lanes

/-- info: 'Rv64Verifier.Proofs.Walk.errTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.errTail

/-- info: 'Rv64Verifier.Proofs.Walk.errTail₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.errTail₁

/-- info: 'Rv64Verifier.Proofs.Walk.tfacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tfacts

/-- info: 'Rv64Verifier.Proofs.Walk.ro_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.ro_heap

/-- info: 'Rv64Verifier.Proofs.Walk.walk_spec_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.walk_spec_of

/-- info: 'Rv64Verifier.Proofs.Walk.Rest.stepW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.Rest.stepW

/-- info: 'Rv64Verifier.Proofs.Walk.StepW.transcript' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.StepW.transcript

/-- info: 'Rv64Verifier.Proofs.Walk.TracksR.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.TracksR.bind

/-- info: 'Rv64Verifier.Proofs.Walk.TracksR.done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.TracksR.done

/-- info: 'Rv64Verifier.Proofs.Walk.tail_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tail_tables

/-- info: 'Rv64Verifier.Proofs.Walk.bodyRest_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.bodyRest_tail

/-- info: 'Rv64Verifier.Proofs.Walk.tsArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tsArgs

/-- info: 'Rv64Verifier.Proofs.Walk.tsPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tsPre

/-- info: 'Rv64Verifier.Proofs.Walk.tablePhase_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tablePhase_run

/-- info: 'Rv64Verifier.Proofs.Walk.tablesAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tablesAt_eq

/-- info: 'Rv64Verifier.Proofs.Walk.RowsAt.eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.RowsAt.eq

/-- info: 'Rv64Verifier.Proofs.Walk.formRowsAt_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.formRowsAt_congr

/-- info: 'Rv64Verifier.Proofs.Walk.Rest.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.Rest.result

/-- info: 'Rv64Verifier.Proofs.Walk.tsCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tsCall

/-- info: 'Rv64Verifier.Proofs.Walk.tsArgs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tsArgs_eq

/-- info: 'Rv64Verifier.Proofs.Walk.tsBranch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tsBranch

/-- info: 'Rv64Verifier.Proofs.Walk.r17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r17

/-- info: 'Rv64Verifier.Proofs.Walk.transcriptAt_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.transcriptAt_exists

/-- info: 'Rv64Verifier.Proofs.Walk.claimAt_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.claimAt_congr

/-- info: 'Rv64Verifier.Proofs.Walk.bases_val' depends on axioms: [propext] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.bases_val

/-- info: 'Rv64Verifier.Proofs.Walk.r18Entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r18Entry

/-- info: 'Rv64Verifier.Proofs.Walk.zip_take_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.zip_take_eq

/-- info: 'Rv64Verifier.Proofs.Walk.tableClaims_take_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tableClaims_take_succ

/-- info: 'Rv64Verifier.Proofs.Walk.tableClaims_take_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tableClaims_take_six

/-- info: 'Rv64Verifier.Proofs.Walk.tableClaims_take_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tableClaims_take_done

/-- info: 'Rv64Verifier.Proofs.Walk.tableClaims_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tableClaims_succ

/-- info: 'Rv64Verifier.Proofs.Walk.afterTables_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.afterTables_stages

/-- info: 'Rv64Verifier.Proofs.Walk.CoreR18.stepW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.CoreR18.stepW

/-- info: 'Rv64Verifier.Proofs.Walk.CoreR18.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.CoreR18.store

/-- info: 'Rv64Verifier.Proofs.Walk.claimAt_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.claimAt_keep

/-- info: 'Rv64Verifier.Proofs.Walk.transcript_heapW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.transcript_heapW

/-- info: 'Rv64Verifier.Proofs.Walk.innerClone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.innerClone

/-- info: 'Rv64Verifier.Proofs.Walk.innerStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.innerStore

/-- info: 'Rv64Verifier.Proofs.Walk.innerStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.innerStep

/-- info: 'Rv64Verifier.Proofs.Walk.innerLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.innerLoop

/-- info: 'Rv64Verifier.Proofs.Walk.outerHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.outerHead

/-- info: 'Rv64Verifier.Proofs.Walk.tab3878' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tab3878

/-- info: 'Rv64Verifier.Proofs.Walk.tab387c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tab387c

/-- info: 'Rv64Verifier.Proofs.Walk.endStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.endStep

/-- info: 'Rv64Verifier.Proofs.Walk.claimAt_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.claimAt_move

/-- info: 'Rv64Verifier.Proofs.Walk.tabGrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tabGrow

/-- info: 'Rv64Verifier.Proofs.Walk.tabRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tabRun

/-- info: 'Rv64Verifier.Proofs.Walk.outerStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.outerStep

/-- info: 'Rv64Verifier.Proofs.Walk.outerLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.outerLoop

/-- info: 'Rv64Verifier.Proofs.Walk.r18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r18

/-- info: 'Rv64Verifier.Proofs.Walk.CoreT.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.CoreT.step

/-- info: 'Rv64Verifier.Proofs.Walk.CoreT.stepW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.CoreT.stepW

/-- info: 'Rv64Verifier.Proofs.Walk.CoreT.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.CoreT.store

/-- info: 'Rv64Verifier.Proofs.Walk.CoreT.growOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.CoreT.growOne

/-- info: 'Rv64Verifier.Proofs.Walk.StepW.thenW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.StepW.thenW

/-- info: 'Rv64Verifier.Proofs.Walk.publicInput_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.publicInput_split

/-- info: 'Rv64Verifier.Proofs.Walk.pub_limbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.pub_limbs

/-- info: 'Rv64Verifier.Proofs.Walk.errTailN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.errTailN

/-- info: 'Rv64Verifier.Proofs.Walk.errTailN₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.errTailN₁

/-- info: 'Rv64Verifier.Proofs.Walk.err41cc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.err41cc

/-- info: 'Rv64Verifier.Proofs.Walk.r22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r22

/-- info: 'Rv64Verifier.Proofs.Walk.r19a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r19a

/-- info: 'Rv64Verifier.Proofs.Walk.r19step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r19step

/-- info: 'Rv64Verifier.Proofs.Walk.r19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r19

/-- info: 'Rv64Verifier.Proofs.Walk.r20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r20

/-- info: 'Rv64Verifier.Proofs.Walk.toR21' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.toR21

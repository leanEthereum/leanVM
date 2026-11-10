import Rv64Verifier.Proofs.Walk.R17B
import Rv64Verifier.Proofs.Walk.R17C
import Rv64Verifier.Proofs.Walk.ErrTail
import Rv64Verifier.Proofs.Walk.TailModel
import Rv64Verifier.Proofs.Walk.Keeps
import Rv64Verifier.Proofs.Walk.Spec
import Rv64Verifier.Proofs.Walk.R17E
import Rv64Verifier.Proofs.Walk.R18C
import Rv64Verifier.Proofs.Walk.TailStages

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

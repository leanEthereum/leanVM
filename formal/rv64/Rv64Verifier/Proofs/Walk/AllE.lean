import Rv64Verifier.Proofs.Walk.R21F
import Rv64Verifier.Proofs.Walk.R22All

/-!
# `walk` R21, R22 and the tail: the axioms, Lean's three

`r21` (`AtR21` to the return), `tail_of` (`walk_spec_of`'s `hTail` given R19 and R20, `R19R20`),
`walk_spec_of'` (`WalkSpecO`, for a front that also gives `PlApart`; `LayoutWithin` from
`buildLayoutRust_within`; the openings kept, `openKeep`, and in place for `verify_stacked_opening`,
`openMem_vso`). Assumed: `ExtendSpecE` (`R21A`), `VsoSpec OA` with `OpenBridge OI OA`, and the
callees' contracts.
-/

/-- info: 'Rv64Verifier.Model.LayoutMirror.buildLayoutRust_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.LayoutMirror.buildLayoutRust_within

/-- info: 'Rv64Verifier.Proofs.Walk.openKeep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.openKeep

/-- info: 'Rv64Verifier.Proofs.Walk.openMem_vso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.openMem_vso

/-- info: 'Rv64Verifier.Proofs.Walk.kp_verifyStackedOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.kp_verifyStackedOpening

/-- info: 'Rv64Verifier.Proofs.Walk.r21ring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r21ring

/-- info: 'Rv64Verifier.Proofs.Walk.r21alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r21alloc

/-- info: 'Rv64Verifier.Proofs.Walk.placements_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.placements_kept

/-- info: 'Rv64Verifier.Proofs.Walk.r21ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r21ext

/-- info: 'Rv64Verifier.Proofs.Walk.RestN.stepW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.RestN.stepW

/-- info: 'Rv64Verifier.Proofs.Walk.r21vso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r21vso

/-- info: 'Rv64Verifier.Proofs.Walk.r21' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r21

/-- info: 'Rv64Verifier.Proofs.Walk.tail_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tail_of

/-- info: 'Rv64Verifier.Proofs.Walk.walk_spec_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.walk_spec_of'

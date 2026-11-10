import Rv64Verifier.Proofs.Walk.Front
import Rv64Verifier.Proofs.Walk.BcWalk

/-!
# `walk`'s front: the axioms

`front` (`Front.lean`) gives `walk_spec_of`'s `hFront` from DEREF, JUMP and the tables' vector
(`AtDeref` to `AtR10`), `verify_bus_balance`'s contract and `BcWalk`; `frontV` the same with
`verify_bus_balance`'s contract reduced to `Vbb.EqKernelSpec` and its side loop's two stages. The
axioms: Lean's three.
-/

/-- info: 'Rv64Verifier.Proofs.Walk.frontHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.frontHead

/-- info: 'Rv64Verifier.Proofs.Walk.loopSpecs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.loopSpecs

/-- info: 'Rv64Verifier.Proofs.Walk.frontKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.frontKeccak

/-- info: 'Rv64Verifier.Proofs.Walk.frontDeref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.frontDeref

/-- info: 'Rv64Verifier.Proofs.Walk.frontR13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.frontR13

/-- info: 'Rv64Verifier.Proofs.Walk.frontR17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.frontR17

/-- info: 'Rv64Verifier.Proofs.Walk.front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.front

/-- info: 'Rv64Verifier.Proofs.Walk.busBalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.busBalance

/-- info: 'Rv64Verifier.Proofs.Walk.frontV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.frontV

/-- info: 'Rv64Verifier.Proofs.Walk.bcWalkClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.bcWalkClosed

/-- info: 'Rv64Verifier.Proofs.Walk.bcCover_of_aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.bcCover_of_aligned

import Rv64Verifier.Proofs.Walk.Dr12

/-!
# `walk`: DEREF, JUMP and R9

`derefStage` (`AtDeref` to `AtJump`), `jumpStage` (`AtJump` to `AtR9`), `r9` (`AtR9` to `AtR10`),
chained from `AtDeref` (`derefToR10`) and from SET's `state_step` call (`setToR10`). The axioms:
Lean's three.
-/

/-- info: 'Rv64Verifier.Proofs.Walk.derefStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.derefStage

/-- info: 'Rv64Verifier.Proofs.Walk.jumpStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.jumpStage

/-- info: 'Rv64Verifier.Proofs.Walk.r9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r9

/-- info: 'Rv64Verifier.Proofs.Walk.derefToR10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.derefToR10

/-- info: 'Rv64Verifier.Proofs.Walk.setToR10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.setToR10

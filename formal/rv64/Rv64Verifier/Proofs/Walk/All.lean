import Rv64Verifier.Proofs.Walk.Announced

/-!
# `walk`: what is proved so far

`WalkSpec` (`Contracts.lean`) is stated; `start` runs the prologue and `Transcript::new` to the
first `next_scalars`, the transcript at `tp` then standing for `TState.init` on every proof the
memory holds; `toScalars` runs on through `next_scalars(8)` to the announced sizes' check, or
returns `Err` (`exit`, `errExit`). The axioms: Lean's three.
-/

/-- info: 'Rv64Verifier.Proofs.Walk.start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.start

/-- info: 'Rv64Verifier.Proofs.Walk.commit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.commit_run

/-- info: 'Rv64Verifier.Proofs.Walk.KeepsProof.commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.KeepsProof.commit

/-- info: 'Rv64Verifier.Proofs.Walk.Tracks.done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.Tracks.done

/-- info: 'Rv64Verifier.Proofs.Walk.toScalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.toScalars

/-- info: 'Rv64Verifier.Proofs.Walk.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.exit

/-- info: 'Rv64Verifier.Proofs.Walk.walkRust_announced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.walkRust_announced

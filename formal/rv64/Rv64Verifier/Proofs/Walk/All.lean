import Rv64Verifier.Proofs.Walk.Head
import Rv64Verifier.Proofs.Walk.R6
import Rv64Verifier.Proofs.Walk.R6U
import Rv64Verifier.Proofs.Walk.AtDeref

/-!
# `walk`: what is proved so far

`WalkSpec` (`Contracts.lean`) is stated; `start` runs the prologue and `Transcript::new` to the
first `next_scalars`, the transcript at `tp` then standing for `TState.init` on every proof the
memory holds; `toScalars` runs on through `next_scalars(8)` to the announced sizes' check, or
returns `Err` (`exit`, `errExit`); `high` checks their high limbs, `rowsStage` fills `table_rows`
and checks the rate, `headStage` runs `build_layout`'s head to `0x80001338` (`Head`: the
conditions of `buildLayoutRust`'s `if`); `r5` runs `table_log_heights` to `state_step`'s call
(`AtR5`), `r6a` from there through `state_step`, the operands and `bytecode` to the first
`keccak_cell_lanes` (`AtR6a`); `keccakLoop` from there through both `keccak_cell_lanes` calls and
the 26-cell loop to `0x80001f00`, the `Flushes` at `sp + 1168` holding `flushes_keccak()`; `r7` from there
through KECCAK's padding row (`keccak_f` of zeros) and the tables' buffer to the first `flushes_arith`
(`M8`, the KECCAK `Table` finished), `xorStage` and `mulStage` through the XOR and MUL `Table`s to
SET's `state_step`, `setHead` through it and the operands' allocation to SET's first `col`, `setStage` through the SET `Table` to DEREF's first `col` (`setStage_atDeref`: `AtDeref`). The axioms: Lean's three.
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

/-- info: 'Rv64Verifier.Proofs.Walk.high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.high

/-- info: 'Rv64Verifier.Proofs.Walk.rowsStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.rowsStage

/-- info: 'Rv64Verifier.Proofs.Walk.headStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.headStage

/-- info: 'Rv64Verifier.Proofs.Walk.pow2_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.pow2_word

/-- info: 'Rv64Verifier.Proofs.Walk.pop_smear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.pop_smear

/-- info: 'Rv64Verifier.Proofs.Walk.r5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r5

/-- info: 'Rv64Verifier.Proofs.Walk.r6a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r6a

/-- info: 'Rv64Verifier.Proofs.Walk.keccakLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.keccakLoop

/-- info: 'Rv64Verifier.Proofs.Walk.r7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r7

/-- info: 'Rv64Verifier.Proofs.Walk.xorStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.xorStage

/-- info: 'Rv64Verifier.Proofs.Walk.mulStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.mulStage

/-- info: 'Rv64Verifier.Proofs.Walk.setHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.setHead

/-- info: 'Rv64Verifier.Proofs.Walk.setStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.setStage

/-- info: 'Rv64Verifier.Proofs.Walk.setStage_atDeref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.setStage_atDeref

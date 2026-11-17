/-
  LeanVM.Compiler.Sound

  The Lean back end's correctness: the end theorems, checked against their statements, and their
  axioms.
-/

module

public import LeanVM.Compiler.Sound.Main
public import LeanVM.Compiler.Sound.Cut

/-!
# The back end's correctness

The compiler's back end in Lean (`Compiler.Place`, `Emit`, `Assemble`) is correct, control flow
included, for every trace: `placeSound` proves `PlaceSoundStmt`, and the end statements hold for
every program (`fnSound`, `programSound`).

By pass:

* **assembly** (`Sound/Asm.lean`): `assemble_fetch`, the program holds at `entry + i` the
  resolved instruction `i` of each function; `layout_consecutive`; `gpowTable_spec`;
* **emission** (`Sound/Ops.lean`, `Fills.lean`, `Sem.lean`, `Run.lean`): `emitFn_ops`,
  `emitFn_fills`, `emitBlockSize`; `PStmt.sem_of_run`, a halting run through a placed statement's
  instructions has its meaning, calls by the callees' contracts at fewer steps; `lowered_sound`
  composes it with assembly;
* **placement** (`Sound/Pool.lean` to `Fn.lean`): `placeAtom_spec` (every atom), `placeBlock_lays`
  (every statement and block, chains of `match`es included, `Sound/Chain.lean`), `placeFn_sound`
  (`PlaceFnSound` on every trace), `placeSound`.

And composed (`Sound/Program.lean`, `Main.lean`):

* `fn_sound`: a function's contract, `FunSpecLtReached` of `World.Pre` and `World.Post`, for runs
  shorter than `n + 1` from every contract for runs shorter than `n`;
* `program_sound`: a halting run of the compiled program from `(g^0, 1)` makes `main`'s core body
  hold under the valuation by places; `program_rel`: hence `Core.Program.Rel` of `main`;
* `World.params_vf`: at every frame, a function's parameters are its argument words under the
  valuation by places.

And the guest's equation by pieces (`Sound/Piece.lean`, `Compiles.lean`): `pieceOk_spec`, what a
kernel-checked piece of one function says, and `compiles_of_pieces`, a program compiled from the
pieces of its functions and checks on numbers (`lowerProgram` succeeds and the assembled functions
are the given ones); `placed_locs_of_pieces`, `world_locs_of_pieces`, the places of each function's values; and a
function's piece from parts, its walk cut between top-level statements (`Sound/Cut.lean`,
`pieceAt_of_cut`).

No certificate enters: the hypotheses are that `lowerProgram` succeeded (`World.Compiled`), the
memory is within the address space, and the functions' obligations (`World.Obligations`: selectors
in range and callees' preconditions, each given what precedes it).
-/

open LeanVM.Compiler

example : EmitBlockSize := emitBlockSize

example {κ : ℕ} (W : World κ) (hW : W.Compiled) (hκ : κ < 64) (tf : TracedFn) (htf : tf ∈ W.p)
    (hne : tf.core.name ≠ "main") (hobl : W.Obligations tf) : W.FnSound tf :=
  fn_sound hW hκ htf hne hobl

example : PlaceSoundStmt := placeSound

example : FnSoundStmt := fnSound

example : ProgramSoundStmt := programSound

/-- info: 'LeanVM.Compiler.assemble_fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.assemble_fetch

/-- info: 'LeanVM.Compiler.layout_consecutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.layout_consecutive

/-- info: 'LeanVM.Compiler.gpowTable_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.gpowTable_spec

/-- info: 'LeanVM.Compiler.emitBlockSize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.emitBlockSize

/-- info: 'LeanVM.Compiler.emitFn_ops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.emitFn_ops

/-- info: 'LeanVM.Compiler.emitFn_fills' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.emitFn_fills

/-- info: 'LeanVM.Compiler.PStmt.sem_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.PStmt.sem_of_run

/-- info: 'LeanVM.Compiler.lowered_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.lowered_sound

/-- info: 'LeanVM.Compiler.placeAtom_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.placeAtom_spec

/-- info: 'LeanVM.Compiler.placeBlock_lays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.placeBlock_lays

/-- info: 'LeanVM.Compiler.placeFn_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.placeFn_sound

/-- info: 'LeanVM.Compiler.placeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.placeSound

/-- info: 'LeanVM.Compiler.fn_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.fn_sound

/-- info: 'LeanVM.Compiler.fn_sound_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.fn_sound_plain

/-- info: 'LeanVM.Compiler.program_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.program_sound

/-- info: 'LeanVM.Compiler.program_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.program_rel

/-- info: 'LeanVM.Compiler.program_sound_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.program_sound_valid

/-- info: 'LeanVM.Compiler.fnSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.fnSound

/-- info: 'LeanVM.Compiler.programSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.programSound


/-- info: 'LeanVM.Compiler.World.params_vf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.World.params_vf

/-- info: 'LeanVM.Compiler.pieceOk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.pieceOk_spec

/-- info: 'LeanVM.Compiler.compiles_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.compiles_of_pieces

/-- info: 'LeanVM.Compiler.placed_locs_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.placed_locs_of_pieces

/-- info: 'LeanVM.Compiler.world_locs_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.world_locs_of_pieces

/-- info: 'LeanVM.Compiler.pieceAt_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Compiler.pieceAt_of_cut

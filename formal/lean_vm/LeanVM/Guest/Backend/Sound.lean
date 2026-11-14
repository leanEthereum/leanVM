/-
  LeanVM.Guest.Backend.Sound

  The Lean back end's correctness: the end theorems, checked against their statements, and their
  axioms.
-/

module

public import LeanVM.Guest.Backend.Sound.Main

/-!
# The back end's correctness

The compiler's back end in Lean (`Backend.Place`, `Emit`, `Assemble`) is correct, control flow
included, for every trace with no `chain` event: a chain of `match`es is the one construct whose
placement is not proved, and its statement is `PlaceSoundStmt` (`Sound/Spec.lean`), from which the
end statements follow for every trace (`fnSoundStmt_of_place`, `programSoundStmt_of_place`).

By pass:

* **assembly** (`Sound/Asm.lean`): `assemble_fetch`, the program holds at `entry + i` the
  resolved instruction `i` of each function; `layout_consecutive`; `gpowTable_spec`;
* **emission** (`Sound/Ops.lean`, `Fills.lean`, `Sem.lean`, `Run.lean`): `emitFn_ops`,
  `emitFn_fills`, `emitBlockSize`; `PStmt.sem_of_run`, a halting run through a placed statement's
  instructions has its meaning, calls by the callees' contracts at fewer steps; `lowered_sound`
  composes it with assembly;
* **placement** (`Sound/Pool.lean` to `Fn.lean`): `placeAtom_spec` (every atom), `placeBlock_lays`
  (every statement and block), `placeFn_sound` (`PlaceFnSound` for a trace with no `chain`).

And composed (`Sound/Program.lean`, `Main.lean`):

* `fn_sound`: a function's contract, `FunSpecLtReached` of `World.Pre` and `World.Post`, for runs
  shorter than `n + 1` from every contract for runs shorter than `n`;
* `program_sound`: a halting run of the compiled program from `(g^0, 1)` makes `main`'s core body
  hold under the valuation by places; `program_rel`: hence `Core.Program.Rel` of `main`.

No certificate enters: the hypotheses are that `lowerProgram` succeeded (`World.Compiled`), the
memory is within the address space, and the functions' obligations (`World.Obligations`: selectors
in range and callees' preconditions, each given what precedes it).
-/

open LeanVM.Guest.Backend

example : EmitBlockSize := emitBlockSize

example {κ : ℕ} (W : World κ) (hW : W.Compiled) (hκ : κ < 64) (tf : TracedFn) (htf : tf ∈ W.p)
    (hne : tf.core.name ≠ "main") (hnc : NoChain tf) (hobl : W.Obligations tf) : W.FnSound tf :=
  fn_sound hW hκ htf hne hnc hobl

example (h : PlaceSoundStmt) : FnSoundStmt := fnSoundStmt_of_place h

example (h : PlaceSoundStmt) : ProgramSoundStmt := programSoundStmt_of_place h

/-- info: 'LeanVM.Guest.Backend.assemble_fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.assemble_fetch

/-- info: 'LeanVM.Guest.Backend.layout_consecutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.layout_consecutive

/-- info: 'LeanVM.Guest.Backend.gpowTable_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.gpowTable_spec

/-- info: 'LeanVM.Guest.Backend.emitBlockSize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.emitBlockSize

/-- info: 'LeanVM.Guest.Backend.emitFn_ops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.emitFn_ops

/-- info: 'LeanVM.Guest.Backend.emitFn_fills' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.emitFn_fills

/-- info: 'LeanVM.Guest.Backend.PStmt.sem_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.PStmt.sem_of_run

/-- info: 'LeanVM.Guest.Backend.lowered_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.lowered_sound

/-- info: 'LeanVM.Guest.Backend.placeAtom_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.placeAtom_spec

/-- info: 'LeanVM.Guest.Backend.placeBlock_lays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.placeBlock_lays

/-- info: 'LeanVM.Guest.Backend.placeFn_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.placeFn_sound

/-- info: 'LeanVM.Guest.Backend.fn_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.fn_sound_of

/-- info: 'LeanVM.Guest.Backend.fn_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.fn_sound

/-- info: 'LeanVM.Guest.Backend.fn_sound_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.fn_sound_plain

/-- info: 'LeanVM.Guest.Backend.program_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.program_sound_of

/-- info: 'LeanVM.Guest.Backend.program_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.program_sound

/-- info: 'LeanVM.Guest.Backend.program_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.program_rel

/-- info: 'LeanVM.Guest.Backend.program_sound_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.program_sound_valid

/-- info: 'LeanVM.Guest.Backend.fnSoundStmt_of_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.fnSoundStmt_of_place

/-- info: 'LeanVM.Guest.Backend.programSoundStmt_of_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.programSoundStmt_of_place


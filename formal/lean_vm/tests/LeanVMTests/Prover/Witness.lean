import Statement.Prover.Columns
import LeanVM.Prover.Witness

/-!
# Tests: the executable witness on a toy run

A program of two slots, `SET [g^2] = 5` then the last slot, run one step from the initial state on
a memory of `2^16` words holding `5` at word `2`: `checkTrace` accepts it (and rejects the same
memory run for two steps), its counts are one `SET_CONSTANT`, and `witness?` builds its sizes, its
columns (word `2` read once: its finalize count is `g`) and its stack of `2^μ` cells.
-/

namespace LeanVMTests.Prover.Witness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover

/-- `SET [g^2] = 5`, then the last slot. -/
def toyProg : LeanIsaProgram :=
  ⟨1, by decide, fun i ↦ if i.val = 0 then .setConstant (addressOfIndex 2) (E.ofLimbs (K.ofBits 5) 0 0)
    else .setConstant (addressOfIndex 3) 0⟩

/-- The zero public input. -/
def toyInput : PublicInput := ⟨fun _ ↦ 0⟩

/-- `2^16` words, `5` at word `2`. -/
def toyImage : MemoryImage 16 := fun i ↦ if i.val = 2 then E.ofLimbs (K.ofBits 5) 0 0 else 0

/-- The run of one step. -/
def toyTrace : Execution toyProg := ⟨16, toyImage, 1⟩

/-- The same memory, two steps: not a valid execution. -/
def toyTrace2 : Execution toyProg := ⟨16, toyImage, 2⟩

#guard checkTrace toyProg toyInput toyTrace
#guard !checkTrace toyProg toyInput toyTrace2
#guard (runSteps (LeanVM.Extraction.powIndex 16) (LeanVM.Extraction.powIndex 1) toyProg
  toyTrace).map (fun st ↦ opCount st .setConstant) == some 1
#guard
  match witness? toyProg toyInput toyTrace with
  | some W => W.rows == [0, 0, 1, 0, 0, 0] && W.layout.logMemory == 16 &&
      W.stack.size == 2 ^ W.layout.stackLog &&
      W.cols.size == 165 && (W.cols.getD 3 #[]).getD 2 0 == g &&
      (W.cols.getD 3 #[]).getD 3 0 == 1
  | none => false

/-- info: 'LeanVM.Prover.witness?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Prover.witness?_spec

/-- info: 'LeanVM.Prover.childFor_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Prover.childFor_trace

/-- info: 'LeanVM.Prover.checkTrace_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Prover.checkTrace_iff

/-- info: 'LeanVM.Prover.isSome_witness?_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Prover.isSome_witness?_iff

end LeanVMTests.Prover.Witness

import LeanVM.Compiler.Invariants
import LeanVMTests.Guest.Programs

/-!
# The back end on the compiler's test programs

Every `crates/zkdsl/tests/programs/*.py` compiles through `Expand` and the back end, and
the back end's invariants hold of its traced expansion (`Compiler.invariants`); and the sizes of
the compiled programs are pinned. That each was the Rust compiler's program, instruction for
instruction and hint for hint, was the Rust test `crates/zkdsl_compiler/tests/suite/lean_backend.rs`
(leanVM `6363526c0`) until that compiler's code generation was deleted; the exports
`lake exe guest-backend export programs` writes are what the Rust tests prove now, and the whole
guest is `lake exe guest-backend check`.
-/

open LeanVM.Guest LeanVM.Core LeanVM.Compiler LeanVM.Semantics

namespace LeanVMTests.Compiler.Programs

/-- The back end's invariants hold of the traced expansion. -/
def checksPass (p : Source.Program) : Bool :=
  match Expand.expandProgramTraced p with
  | .ok traced =>
      match invariants traced with
      | .ok checks => checks.all (·.2)
      | .error _ => false
  | .error _ => false

#guard LeanVMTests.Guest.Programs.all.all fun t => checksPass t.program

/-- A compiled program's instructions, padded size and `main` frame. -/
def shape (p : Source.Program) : Option (Nat × Nat × Nat) :=
  match LeanVM.Compiler.compile p with
  | .ok a => some (a.code.size, a.size, a.mainFrame)
  | .error _ => none

#guard LeanVMTests.Guest.Programs.all.map (fun t => shape t.program) ==
  [(64, 128, 27), (58, 64, 24), (42, 64, 14), (1048, 2048, 20), (49, 64, 13), (25, 32, 23),
   (16, 32, 17), (18, 32, 17), (10, 16, 9), (25, 32, 20), (69, 128, 27), (134, 256, 33),
   (82, 128, 16), (68, 128, 24), (37, 64, 30), (54, 64, 20), (118, 128, 36)].map some

/-- The code of a test program. -/
def codeOf (name : String) : Option (List OffsetInstruction) :=
  (LeanVMTests.Guest.Programs.all.find? (·.name == name)).bind fun t =>
    match LeanVM.Compiler.compile t.program with
    | .ok a => some a.code.toList
    | .error _ => none

-- `identities.py` whole: a pooled constant, a range check, an assertion (its two values one cell)
-- and the halt.
#guard codeOf "identities" == some [
  .set 2 4 0, .set 2 4 0, .deref 2 0 4 .cell, .mul 2 3 2, .deref 3 0 5 .cell,
  .set 6 0 0, .set 6 0 0, .set 7 1 0, .set 8 32768 0, .jump 7 8 7]

end LeanVMTests.Compiler.Programs

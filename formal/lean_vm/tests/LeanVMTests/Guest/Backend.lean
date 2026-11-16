import LeanVM.Guest.Backend.Invariants
import LeanVMTests.Guest.Programs

/-!
# The back end on the compiler's test programs

Every `crates/zkdsl_compiler/tests/programs/*.py` compiles through `Expand` and the back end, and
the back end's invariants hold of its traced expansion (`Backend.invariants`); and the sizes of
the compiled programs are pinned. That each is the Rust compiler's program, instruction for
instruction and hint for hint, is the Rust test `crates/zkdsl_compiler/tests/suite/lean_backend.rs`
on the exports `lake exe guest-backend export programs` writes; the whole guest is
`lake exe guest-backend check`.
-/

open LeanVM.Guest LeanVM.Guest.Backend LeanVM.Semantics

namespace LeanVMTests.Guest.Backend

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
  match Backend.compile p with
  | .ok a => some (a.code.size, a.size, a.mainFrame)
  | .error _ => none

#guard LeanVMTests.Guest.Programs.all.map (fun t => shape t.program) ==
  [(64, 128, 27), (62, 64, 24), (43, 64, 15), (49, 64, 13), (26, 32, 24), (16, 32, 17), (21, 32, 20),
   (10, 16, 9), (69, 128, 27), (135, 256, 34), (82, 128, 16), (69, 128, 24), (37, 64, 33),
   (56, 64, 22), (121, 128, 39)].map some

/-- The code of a test program. -/
def codeOf (name : String) : Option (List OffsetInstruction) :=
  (LeanVMTests.Guest.Programs.all.find? (·.name == name)).bind fun t =>
    match Backend.compile t.program with
    | .ok a => some a.code.toList
    | .error _ => none

-- `identities.py` whole: a pooled constant, a range check, an assertion and the halt.
#guard codeOf "identities" == some [
  .set 2 4 0, .set 3 1 0, .mul 2 3 2, .deref 2 0 5 .cell, .mul 2 4 2, .deref 4 0 6 .cell,
  .set 7 0 0, .mul 7 3 7, .set 8 32768 0, .jump 3 8 3]

end LeanVMTests.Guest.Backend

import Statement.Data.Bytecode
import LeanVM.Guest.Code
import LeanVM.Guest.Data.Source
import LeanVMTests.Guest.Manifest
import LeanVMTests.Guest.Programs

/-!
# The guest's generated data against the Rust's manifest

`scripts/guest-export` writes the compiled guest (`Statement/Data/Bytecode*.lean`), its source
AST (`Data/Source.lean`), the compiler's test programs (`Programs.lean`) and what the Rust reports
of the deployed guest (`Manifest.lean`). Recomputed here from the Lean data: the log size, the code
length, the function count, the instructions of each opcode, the source's placeholders' log size.
That the assembled `guest` is the bytecode the Rust proves, every instruction, is
`lake exe node-vectors` (its Fiat-Shamir IV against `Manifest.fsSeed`).
-/

namespace LeanVMTests.Guest.Data

open LeanVM.Guest LeanVM.Guest.Data

/-- The opcode index of an instruction: `XOR`, `MUL`, `SET`, `DEREF`, `JUMP`, `KECCAK`. -/
def opIdx : OffsetInstruction → Nat
  | .xor .. => 0
  | .mul .. => 1
  | .set .. => 2
  | .deref .. => 3
  | .jump .. => 4
  | .keccak .. => 5

/-- The instructions of each opcode in the padded bytecode. -/
def opcodeCounts : List Nat :=
  let code := functions.flatMap (·.chunks.flatten)
  let pad := 2 ^ logSize - codeLen
  (List.range 6).map fun i ↦ (code.filter (opIdx · == i)).length + if i == 2 then pad else 0

#guard logSize = Manifest.logSize
#guard codeLen = Manifest.codeLen
#guard functions.length = Manifest.functionCount
#guard (functions.map (·.instructionCount)).sum = codeLen
#guard opcodeCounts = Manifest.opcodeCounts

/- The source's placeholders are those of the bytecode's size. -/
#guard bytecodeLog = logSize

/- The guest's source: its functions, constant arrays, and `main` among them. -/
#guard guest.funcs.length = 129
#guard guest.constArrays.length = 80
#guard guest.funcs.any (·.name == "main")

/- The compiler's fifteen test programs. -/
#guard Programs.all.length = 15

end LeanVMTests.Guest.Data

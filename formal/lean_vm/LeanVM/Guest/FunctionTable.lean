/-
  LeanVM.Guest.FunctionTable

  The compiled functions' table, chunked as stored.
-/

module

public import Statement.Data.Bytecode
public import LeanVM.Guest.Code

/-!
# The function table, chunked

`functions_wellChunked`: every compiled function's chunks hold exactly its instructions, checked
once by the kernel. Apart from `Bytecode.lean` (the program `guest`, which imports the statement
of the guest), so that the symbolic executor's fetch (`ExecC.lean`), and with it the kernel-checked
certificates, do not import that statement.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- Every function's chunks hold exactly its instructions. -/
theorem functions_wellChunked : Data.functions.all (fun f ↦ chunked chunkSize f.chunks f.instructionCount) = true := by
  decide +kernel

end
end LeanVM.Guest

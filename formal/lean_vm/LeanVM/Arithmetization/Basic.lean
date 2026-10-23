module

public import LeanVM.Semantics.Lemmas

/-!
# Arithmetization

This layer holds the bytecode encoding (`Bytecode`), the bus channels (`Channels`), the six
opcode tables (`Tables/`), and the three boundary blocks (`Boundary`), all Lean modules
over Clean, and will hold the constraint statement, witness generation, and the
refinement theorems connecting satisfying assignments to `LeanVM.Semantics` executions.
-/

namespace LeanVM.Arithmetization

public section

end
end LeanVM.Arithmetization

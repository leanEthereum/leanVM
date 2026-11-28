module

public import LeanVM.Guest.Complete.CallComplete
public import LeanVM.Guest.Limits

/-!
# The deployed guest's bytecode and seed

`guestBytecode` and `guestSeed`, the stacked program and the seed `main`'s completeness is stated at.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.B1

@[expose] public section

/-- The guest's stacked program. -/
abbrev guestBytecode : List K := bytecodeWords guestProgram

/-- The deployed seed. -/
abbrev guestSeed : Digest := deployedSeed guestProgram

end
end LeanVM.Guest.Complete

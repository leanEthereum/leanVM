module

public import LeanVM.Guest.CoreMode.SigTrie
public import LeanVM.Guest.Data.Pows
public import LeanVM.Guest.CoreMode.GlueG

/-!
# A core-route function's environment

What the frame interface (`Mode.Cert`) of a function on the core route is told of the program, from the
core route's own data: its callees' signatures by key (`sigTrie`), the guest's powers, jump table and
halting pc (`envOf`; the jump table's bounds and the halting pc, constants of the program, from the glue `GlueG`). A function's signature (`Fn.«k».csig`, `CoreMode/Sig/<pack>.lean`) and its
certificate's data (`Fn.«k».envC`, `funC`, in its frame walk's module) are written by
`scripts/core-mode/frame_gen.py`.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- **The guest's program as a core-route function's certificate has it**, its callees' signatures `l`. -/
noncomputable def envOf (l : List Mode.Sig) : Mode.Env :=
  ⟨Data.powTree, Data.jtTrie, jtLo, jtHi, sigTrie l, haltPc⟩

end

end LeanVM.Guest.CoreMode

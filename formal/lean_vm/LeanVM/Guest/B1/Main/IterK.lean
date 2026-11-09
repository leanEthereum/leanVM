/-
  LeanVM.Guest.B1.Main.IterK

  A statically bounded loop helper's words per iteration, its run's phantom frame apart (`iterK`).
-/

module

namespace LeanVM.Guest.B1.Main

@[expose] public section

/-- **A static loop helper's words per iteration, its run's phantom frame apart**: `SK g` charges
each iteration the phantom frame `fs g` that a run leaves once (its last iteration's untaken tail
call); a call site charges `iterK fs SK g` per iteration and `fs g` once for the run. -/
def iterK (fs SK : String → Nat) (g : String) : Nat := SK g - fs g

end
end LeanVM.Guest.B1.Main

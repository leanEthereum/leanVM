/-
  LeanVM.Guest.B1.Terminal.Interface

  `InterfaceP.lean`'s statements at the guest's `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Terminal.InterfaceP

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `check_opening_terminal_SpecP` at the guest's `coreProgram`. -/
abbrev check_opening_terminal_Spec (rd : Reader) : Prop := check_opening_terminal_SpecP coreProgram rd

end
end LeanVM.Guest.B1.VerifySub

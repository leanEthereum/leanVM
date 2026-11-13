/-
  LeanVM.Guest.B1.Gkr.Interface

  `InterfaceP.lean`'s statements at the guest's `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Gkr.InterfaceP

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_bus_gkr_SpecP` at the guest's `coreProgram`. -/
abbrev verify_bus_gkr_Spec (rd : Reader) : Prop := verify_bus_gkr_SpecP coreProgram rd

end
end LeanVM.Guest.B1.Tables

/-
  LeanVM.Guest.B1.Placement.Interface

  `InterfaceP.lean`'s statements at the guest's `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Placement.InterfaceP

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `certify_placement_SpecP` at the guest's `coreProgram`. -/
abbrev certify_placement_Spec (rd : Reader) : Prop := certify_placement_SpecP coreProgram rd

end
end LeanVM.Guest.B1.Tables

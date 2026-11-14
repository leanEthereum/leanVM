/-
  LeanVM.Guest.B1.Tables.Interface

  `InterfaceP.lean`'s statements at the guest's `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Tables.InterfaceP

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `padding_weight_SpecP` at the guest's `coreProgram`. -/
abbrev padding_weight_Spec : Prop := padding_weight_SpecP coreProgram

/-- `padding_weight_complete_SpecP` at the guest's `coreProgram`. -/
abbrev padding_weight_complete_Spec : Prop := padding_weight_complete_SpecP coreProgram

/-- `verify_tables_SpecP` at the guest's `coreProgram`. -/
abbrev verify_tables_Spec (bytecode : List K) (rd : Reader) : Prop := verify_tables_SpecP coreProgram bytecode rd

end
end LeanVM.Guest.B1.Tables

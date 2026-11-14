/-
  LeanVM.Guest.B1.KeccakGkr.Interface

  `InterfaceP.lean`'s statements at the guest's `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.KeccakGkr.InterfaceP

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `keccak_plain_rounds_SpecP` at the guest's `coreProgram`. -/
abbrev keccak_plain_rounds_Spec : Prop := keccak_plain_rounds_SpecP coreProgram

/-- `keccak_plain_rounds_complete_SpecP` at the guest's `coreProgram`. -/
abbrev keccak_plain_rounds_complete_Spec : Prop := keccak_plain_rounds_complete_SpecP coreProgram

/-- `keccak_layer_SpecP` at the guest's `coreProgram`. -/
abbrev keccak_layer_Spec (rd : Reader) : Prop := keccak_layer_SpecP coreProgram rd

/-- `verify_keccak_SpecP` at the guest's `coreProgram`. -/
abbrev verify_keccak_Spec (rd : Reader) : Prop := verify_keccak_SpecP coreProgram rd

end
end LeanVM.Guest.B1.VerifySub

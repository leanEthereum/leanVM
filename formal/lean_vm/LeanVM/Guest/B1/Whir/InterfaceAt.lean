/-
  LeanVM.Guest.B1.Whir.InterfaceAt

  `open_stacked`'s statements at the guest's `coreProgram`.
-/

module

public import LeanVM.Guest.B1.Whir.InterfaceW
public import LeanVM.Guest.B1.Main.Frames
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`open_stacked` is sound** (`Interface.lean`), in the guest's `coreProgram`. -/
abbrev open_stacked_sound_Spec : Prop := open_stacked_sound_SpecP coreProgram

/-- **`open_stacked` is sound with its witness `osW`** (`InterfaceW.lean`), in the guest's
`coreProgram`. -/
abbrev open_stacked_sound_w_Spec
    (osW : Reader → ℕ → ℕ → Val → FrameMap → List E × List (List Opening)) : Prop :=
  open_stacked_sound_w_SpecP coreProgram osW

end
end LeanVM.Guest.B1.Whir

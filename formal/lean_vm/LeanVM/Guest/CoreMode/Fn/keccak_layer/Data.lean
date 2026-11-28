/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.Data

  `keccak_layer`'s own routing data (`CoreMode/FnReg.lean`): its caller.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.keccak_layer

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its caller** (`Res.callersG`): `verify_keccak`, for both specializations. -/
def stCallers : List (String × String) :=
  [(name% «keccak_layer__L0», name% «verify_keccak»), (name% «keccak_layer__L1», name% «verify_keccak»)]

end

end LeanVM.Guest.CoreMode.Own.keccak_layer

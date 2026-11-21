/-
  LeanVM.Guest.CoreMode.Fn.da_pad.Data

  `da_pad`'s own routing data (`CoreMode/FnReg.lean`): its caller.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.da_pad

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its caller** (`Res.callersG`): `da_verify`. -/
def stCallers : List (String × String) := [(name% «da_pad», name% «da_verify»)]

end

end LeanVM.Guest.CoreMode.Own.da_pad

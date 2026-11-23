/-
  LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.Data

  `verify_bus_gkr`'s own routing data (`CoreMode/FnReg.lean`): its caller.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.verify_bus_gkr

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its caller** (`Res.callersG`): `verify_sub`. -/
def stCallers : List (String × String) := [(name% «verify_bus_gkr», name% «verify_sub»)]

end

end LeanVM.Guest.CoreMode.Own.verify_bus_gkr

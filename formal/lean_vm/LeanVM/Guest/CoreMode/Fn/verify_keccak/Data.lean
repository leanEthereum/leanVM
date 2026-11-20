/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.Data

  `verify_keccak`'s own routing data (`CoreMode/FnReg.lean`): its caller.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.verify_keccak

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its caller** (`Res.callersG`): `verify_sub`. -/
def stCallers : List (String × String) := [(name% «verify_keccak», name% «verify_sub»)]

end

end LeanVM.Guest.CoreMode.Own.verify_keccak

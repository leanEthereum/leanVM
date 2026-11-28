/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Data

  `verify_sub`'s own routing data (`CoreMode/FnReg.lean`): the callee it carries a fact down to, its nonzero divisors.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its callee's caller** (`Res.callersG`): `verify_keccak`'s, whose `tau_g` it certifies (`EndExec.VkQ`). -/
def stCallers : List (String × String) := [(name% «verify_keccak», name% «verify_sub»)]

/-- **Its divisors, nonzero** (`CoreMode.FnReg.nzs`): the frame walk's residual divisors, the link's cycle count `240`
and its vanishing count `652` (`EndExec.nzValA_vs240`, `nzValA_vs652`). -/
def nzs : List (String × V) := [(name% «verify_sub», .n 240), (name% «verify_sub», .n 652)]

end

end LeanVM.Guest.CoreMode.Own.verify_sub

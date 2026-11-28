/-
  LeanVM.Guest.CoreMode.Fn.certify_stack.Data

  `certify_stack`'s own routing data (`CoreMode/FnReg.lean`): its nonzero divisor.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.certify_stack

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its divisor, nonzero** (`CoreMode.FnReg.nzs`): rank `1`'s key, its value `182` (`B1.Stack.csRank`'s `s + 6` at
`s = 176`), the frame walk's residual divisor. -/
def nzs : List (String × V) := [(name% «certify_stack», .n 182)]

end

end LeanVM.Guest.CoreMode.Own.certify_stack

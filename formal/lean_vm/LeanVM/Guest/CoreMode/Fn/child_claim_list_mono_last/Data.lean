/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono_last.Data

  `child_claim_list_mono_last`'s own routing data (`CoreMode/FnReg.lean`): its nonzero divisor.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.child_claim_list_mono_last

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its divisor, nonzero** (`CoreMode.coreNzs`): `child_claim_list_mono_last__L0`'s parameter `1`. -/
def nzs : List (String × V) := [(name% «child_claim_list_mono_last__L0», .n 1)]

end

end LeanVM.Guest.CoreMode.Own.child_claim_list_mono_last

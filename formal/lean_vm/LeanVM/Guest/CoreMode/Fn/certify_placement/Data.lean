/-
  LeanVM.Guest.CoreMode.Fn.certify_placement.Data

  `certify_placement`'s own routing data (`CoreMode/FnReg.lean`): its nonzero divisor.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«certify_placement»

namespace LeanVM.Guest.CoreMode.Own.certify_placement

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its divisor, nonzero** (`CoreMode.coreNzs`): its value `155`. -/
def nzs : List (String × V) := [(name% «certify_placement», .n (val% «certify_placement» "key@2"))]

end

end LeanVM.Guest.CoreMode.Own.certify_placement

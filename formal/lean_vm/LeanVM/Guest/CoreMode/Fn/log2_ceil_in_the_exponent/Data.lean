/-
  LeanVM.Guest.CoreMode.Fn.log2_ceil_in_the_exponent.Data

  `log2_ceil_in_the_exponent`'s own routing data (`CoreMode/FnReg.lean`): its nonzero divisors.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.log2_ceil_in_the_exponent

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its divisors, nonzero** (`CoreMode.coreNzs`): two specializations' parameter `0`. -/
def nzs : List (String × V) :=
  [(name% «log2_ceil_in_the_exponent__L0_L34», .n 0), (name% «log2_ceil_in_the_exponent__L16_L34», .n 0)]

end

end LeanVM.Guest.CoreMode.Own.log2_ceil_in_the_exponent

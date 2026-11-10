/-
  LeanVM.Guest.B1.Da.FactorsChk

  `da_factors`' two specializations' bodies, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Factors

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem fac14_ok : facOk Data.core433 14 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fac7_ok : facOk Data.core435 7 8 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

/-
  LeanVM.Guest.B1.Da.FactorsChk

  `da_factors`' two specializations' bodies, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Factors

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem facTop_ok : facOk fn% «da_factors__L13_L7_L0» 13 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem facCell_ok : facOk fn% «da_factors__L6_L7_L128» 6 7 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

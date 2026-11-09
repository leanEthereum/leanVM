/-
  LeanVM.Guest.B1.Da.LevelsChk4

  `da_levels`' specializations k = 8, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.LevelsTab

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_ok8 : dlEntryOk 8 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

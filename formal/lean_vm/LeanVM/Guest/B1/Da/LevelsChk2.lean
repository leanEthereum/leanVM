/-
  LeanVM.Guest.B1.Da.LevelsChk2

  `da_levels`' specializations k = 5, 6, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.LevelsTab

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_ok5 : dlEntryOk 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dl_ok6 : dlEntryOk 6 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

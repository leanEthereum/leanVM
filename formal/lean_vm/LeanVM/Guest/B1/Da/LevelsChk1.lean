/-
  LeanVM.Guest.B1.Da.LevelsChk1

  `da_levels`' specializations k = 3, 4, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.LevelsTab

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_ok3 : dlEntryOk 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dl_ok4 : dlEntryOk 4 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

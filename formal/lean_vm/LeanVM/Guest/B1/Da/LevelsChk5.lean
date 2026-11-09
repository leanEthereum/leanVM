/-
  LeanVM.Guest.B1.Da.LevelsChk5

  `da_levels`' specializations k = 9, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.LevelsTab

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_ok9 : dlEntryOk 9 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

/-
  LeanVM.Guest.B1.Da.LevelsChk0

  `da_levels`' specializations `k ≤ 4`, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.LevelsTab

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_ok0 : dlEntryOk 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dl_ok1 : dlEntryOk 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dl_ok2 : dlEntryOk 2 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

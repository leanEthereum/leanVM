/-
  LeanVM.Guest.B1.Da.ExpandChk

  `da_expand`'s two specializations' bodies, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Expand

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem exp8_ok : expOk Data.core395 7 8 69649 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem exp7_ok : expOk Data.core398 14 7 325 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

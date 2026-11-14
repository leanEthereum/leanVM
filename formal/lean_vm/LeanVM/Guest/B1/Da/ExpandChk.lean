/-
  LeanVM.Guest.B1.Da.ExpandChk

  `da_expand`'s two specializations' bodies, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Expand

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem expCell_ok : expOk fn% «da_expand__L6_L7» 6 7 325 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem expTop_ok : expOk fn% «da_expand__L13_L7» 13 7 325 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da

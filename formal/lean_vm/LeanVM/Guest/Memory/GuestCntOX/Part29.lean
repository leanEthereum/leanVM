module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_996 : kwoxStaticRange 996 11 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_1007 : kwoxStaticRange 1007 11 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest

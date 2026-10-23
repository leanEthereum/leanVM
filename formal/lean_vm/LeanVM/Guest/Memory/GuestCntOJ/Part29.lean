module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_996 : kwojStaticRange 996 11 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_1007 : kwojStaticRange 1007 11 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest

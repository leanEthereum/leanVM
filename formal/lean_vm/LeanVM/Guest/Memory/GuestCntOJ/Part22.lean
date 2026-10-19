module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_782 : kwojStaticRange 782 14 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_796 : kwojStaticRange 796 14 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest

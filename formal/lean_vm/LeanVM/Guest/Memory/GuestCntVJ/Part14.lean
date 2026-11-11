module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1700 : kvjStaticRange 1700 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1712 : kvjStaticRange 1712 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1581 : kvjStaticRange 1581 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1593 : kvjStaticRange 1593 8 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

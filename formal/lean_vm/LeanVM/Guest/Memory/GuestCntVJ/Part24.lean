module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1530 : kvjStaticRange 1530 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1543 : kvjStaticRange 1543 13 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

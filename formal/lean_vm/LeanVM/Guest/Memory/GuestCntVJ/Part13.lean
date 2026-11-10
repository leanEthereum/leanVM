module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1707 : kvjStaticRange 1707 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1720 : kvjStaticRange 1720 15 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

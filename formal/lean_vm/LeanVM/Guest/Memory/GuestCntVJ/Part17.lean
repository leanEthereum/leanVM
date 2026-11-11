module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1343 : kvjStaticRange 1343 11 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1354 : kvjStaticRange 1354 19 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1556 : kvjStaticRange 1556 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1569 : kvjStaticRange 1569 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

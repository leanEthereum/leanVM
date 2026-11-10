module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1759 : kvjStaticRange 1759 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1771 : kvjStaticRange 1771 11 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

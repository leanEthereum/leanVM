module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_644 : kvjStaticRange 644 16 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_660 : kvjStaticRange 660 17 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

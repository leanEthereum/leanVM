module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1479 : kvjStaticRange 1479 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1491 : kvjStaticRange 1491 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

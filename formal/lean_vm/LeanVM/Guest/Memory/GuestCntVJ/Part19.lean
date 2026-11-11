module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1397 : kvjStaticRange 1397 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1415 : kvjStaticRange 1415 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

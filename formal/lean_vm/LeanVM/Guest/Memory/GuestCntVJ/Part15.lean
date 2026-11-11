module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1292 : kvjStaticRange 1292 8 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1300 : kvjStaticRange 1300 11 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

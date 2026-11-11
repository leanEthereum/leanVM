module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1452 : kvjStaticRange 1452 19 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1471 : kvjStaticRange 1471 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

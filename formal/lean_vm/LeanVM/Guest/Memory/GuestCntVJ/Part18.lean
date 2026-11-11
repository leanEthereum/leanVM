module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1373 : kvjStaticRange 1373 14 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1387 : kvjStaticRange 1387 10 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

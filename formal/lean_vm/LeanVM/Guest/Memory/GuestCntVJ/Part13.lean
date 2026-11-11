module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1503 : kvjStaticRange 1503 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1515 : kvjStaticRange 1515 10 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

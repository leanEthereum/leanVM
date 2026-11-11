module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1311 : kvjStaticRange 1311 20 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1331 : kvjStaticRange 1331 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

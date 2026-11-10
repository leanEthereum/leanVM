module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_576 : kvjStaticRange 576 19 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_595 : kvjStaticRange 595 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

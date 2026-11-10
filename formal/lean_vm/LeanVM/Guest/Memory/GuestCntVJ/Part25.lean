module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_649 : kvjStaticRange 649 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_666 : kvjStaticRange 666 17 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1047 : kvjStaticRange 1047 7 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1054 : kvjStaticRange 1054 1 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

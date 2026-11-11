module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1020 : kvjStaticRange 1020 8 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1028 : kvjStaticRange 1028 7 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

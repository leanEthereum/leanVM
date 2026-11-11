module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1119 : kvjStaticRange 1119 14 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1133 : kvjStaticRange 1133 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

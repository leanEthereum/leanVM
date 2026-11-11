module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1016 : kvjStaticRange 1016 9 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1025 : kvjStaticRange 1025 8 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1033 : kvjStaticRange 1033 4 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

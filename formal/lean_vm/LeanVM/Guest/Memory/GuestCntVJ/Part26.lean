module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_766 : kvjStaticRange 766 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_784 : kvjStaticRange 784 20 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_804 : kvjStaticRange 804 24 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_828 : kvjStaticRange 828 22 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

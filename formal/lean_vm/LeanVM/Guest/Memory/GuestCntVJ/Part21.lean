module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_592 : kvjStaticRange 592 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_610 : kvjStaticRange 610 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

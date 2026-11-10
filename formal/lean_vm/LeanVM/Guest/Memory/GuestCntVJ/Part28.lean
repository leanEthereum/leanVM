module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_755 : kvjStaticRange 755 14 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_769 : kvjStaticRange 769 17 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

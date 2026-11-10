module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1735 : kvjStaticRange 1735 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1747 : kvjStaticRange 1747 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1201 : kvjStaticRange 1201 11 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1212 : kvjStaticRange 1212 15 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_345 : kvjStaticRange 345 2 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_347 : kvjStaticRange 347 1 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

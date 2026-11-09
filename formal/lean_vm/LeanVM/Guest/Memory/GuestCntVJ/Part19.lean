module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_520 : kvjStaticRange 520 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_538 : kvjStaticRange 538 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

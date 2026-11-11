module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_677 : kvjStaticRange 677 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_695 : kvjStaticRange 695 16 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

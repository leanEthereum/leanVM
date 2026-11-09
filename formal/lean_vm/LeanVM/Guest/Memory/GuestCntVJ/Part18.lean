module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_461 : kvjStaticRange 461 21 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_482 : kvjStaticRange 482 20 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_502 : kvjStaticRange 502 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

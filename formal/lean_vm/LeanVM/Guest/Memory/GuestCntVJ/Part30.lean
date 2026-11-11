module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_959 : kvjStaticRange 959 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_972 : kvjStaticRange 972 14 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

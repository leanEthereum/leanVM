module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_961 : kvjStaticRange 961 14 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_975 : kvjStaticRange 975 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

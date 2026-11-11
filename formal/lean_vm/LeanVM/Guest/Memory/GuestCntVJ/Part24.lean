module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_711 : kvjStaticRange 711 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_728 : kvjStaticRange 728 17 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

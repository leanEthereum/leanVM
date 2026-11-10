module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_821 : kvjStaticRange 821 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_838 : kvjStaticRange 838 16 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest

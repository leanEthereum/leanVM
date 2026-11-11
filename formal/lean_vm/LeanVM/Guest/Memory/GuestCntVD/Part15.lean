module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1292 : kvdStaticRange 1292 8 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1300 : kvdStaticRange 1300 11 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

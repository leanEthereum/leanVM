module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1479 : kvdStaticRange 1479 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1491 : kvdStaticRange 1491 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

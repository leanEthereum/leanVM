module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1556 : kvdStaticRange 1556 13 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1569 : kvdStaticRange 1569 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

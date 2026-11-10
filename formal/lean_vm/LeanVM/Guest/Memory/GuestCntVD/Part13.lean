module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1707 : kvdStaticRange 1707 13 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1720 : kvdStaticRange 1720 15 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

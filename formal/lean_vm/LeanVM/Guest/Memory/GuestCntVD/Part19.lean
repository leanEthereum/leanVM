module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1397 : kvdStaticRange 1397 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1415 : kvdStaticRange 1415 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

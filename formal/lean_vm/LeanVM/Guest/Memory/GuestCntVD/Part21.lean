module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1452 : kvdStaticRange 1452 19 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1471 : kvdStaticRange 1471 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

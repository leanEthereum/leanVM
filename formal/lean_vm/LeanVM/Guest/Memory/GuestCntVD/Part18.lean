module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1373 : kvdStaticRange 1373 14 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1387 : kvdStaticRange 1387 10 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1433 : kvdStaticRange 1433 8 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1441 : kvdStaticRange 1441 11 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

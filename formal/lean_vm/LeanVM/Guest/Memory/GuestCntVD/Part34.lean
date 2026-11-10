module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_991 : kvdStaticRange 991 14 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1005 : kvdStaticRange 1005 13 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1047 : kvdStaticRange 1047 7 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1054 : kvdStaticRange 1054 1 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1020 : kvdStaticRange 1020 8 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1028 : kvdStaticRange 1028 7 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

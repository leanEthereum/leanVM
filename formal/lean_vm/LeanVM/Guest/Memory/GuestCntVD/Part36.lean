module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1048 : kvdStaticRange 1048 7 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest

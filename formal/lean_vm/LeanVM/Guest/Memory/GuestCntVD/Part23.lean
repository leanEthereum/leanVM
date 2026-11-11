module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1502 : kvdStaticRange 1502 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1514 : kvdStaticRange 1514 16 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
